#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <fcntl.h>
#include <string.h>

#define PI 3.141592653589793
#define GETL getline(&line,&len,in)
#define no 1  /* Ordre du filtre de Buttersworth*/

int NST,NSAMPLES,NHEADER,PW,dn;
float FACQ=1,f1,f2,F1,df,gf,thresh;

int flor(x)
float x;
{
	int y;

	y=(int)x;
	if(y>x) y--;
	return(y);
}


/*
   This computes an in-place complex-to-complex FFT 
   x and y are the real and imaginary arrays of 2^m points.
   dir =  1 gives forward transform
   dir = -1 gives reverse transform 
*/
void FFT(int dir,int m,float *x,float *y)
{
   int n,i,i1,j,k,i2,l,l1,l2;
   float c1,c2,tx,ty,t1,t2,u1,u2,z;

   /* Calculate the number of points */
   n = 1;
   for (i=0;i<m;i++) 
      n *= 2;

   /* Do the bit reversal */
   i2 = n >> 1;
   j = 0;
   for (i=0;i<n-1;i++) {
      if (i < j) {
         tx = x[i];
         ty = y[i];
         x[i] = x[j];
         y[i] = y[j];
         x[j] = tx;
         y[j] = ty;
      }
      k = i2;
      while (k <= j) {
         j -= k;
         k >>= 1;
      }
      j += k;
   }

   /* Compute the FFT */
   c1 = -1.0; 
   c2 = 0.0;
   l2 = 1;
   for (l=0;l<m;l++) {
      l1 = l2;
      l2 <<= 1;
      u1 = 1.0; 
      u2 = 0.0;
      for (j=0;j<l1;j++) {
         for (i=j;i<n;i+=l2) {
            i1 = i + l1;
            t1 = u1 * x[i1] - u2 * y[i1];
            t2 = u1 * y[i1] + u2 * x[i1];
            x[i1] = x[i] - t1; 
            y[i1] = y[i] - t2;
            x[i] += t1;
            y[i] += t2;
         }
         z =  u1 * c1 - u2 * c2;
         u2 = u1 * c2 + u2 * c1;
         u1 = z;
      }
      c2 = sqrt((1.0 - c1) / 2.0);
      if (dir == 1) 
         c2 = -c2;
      c1 = sqrt((1.0 + c1) / 2.0);
   }

   /* Scaling for forward transform */
   if (dir == 1) {
      for (i=0;i<n;i++) {
         x[i] /= n;
         y[i] /= n;
      }
   }
}


void compute_correlation(ar,ai,br,bi,cr,ci,apo,filt,f,NW,rho,dd,sigma,ramp)
float *ar,*ai,*br,*bi,*cr,*ci,*apo,*filt,*rho,*dd,*sigma,*f,*ramp;
int NW;
{
	int n,k,K;
	float stdA=0,stdB=0,maxrho,tmp,ma=0,mb=0;
	double S0,S1,S2,S3,S4,R0,R1,R2,a,b,c;

	for(n=0;n<NW;n++) { 
		ar[n]*=apo[n];
		br[n]*=apo[n];
		ma+=ar[n]; mb+=br[n];
	}
	for(n=0;n<NW;n++) { 
		ar[n]-=(ma/NW);
		br[n]-=(mb/NW);
	}

	FFT(1,PW,ar,ai);
	FFT(1,PW,br,bi);
	for(n=0;n<NW;n++) {
		ar[n]*=filt[n]; ai[n]*=filt[n]; br[n]*=filt[n]; bi[n]*=filt[n];
		stdA+=ar[n]*ar[n]+ai[n]*ai[n];
		stdB+=br[n]*br[n]+bi[n]*bi[n];
	}
	stdA=sqrt(stdA); stdB=sqrt(stdB); *ramp=stdA/stdB;

	for(n=0;n<NW;n++) {
		cr[n]=(ar[n]*br[n]+ai[n]*bi[n])/(NW*stdA*stdB);
		ci[n]=(ar[n]*bi[n]-ai[n]*br[n])/(NW*stdA*stdB);
	}
	FFT(-1,PW,cr,ci);
	for(maxrho=-10,n=0;n<NW;n++) 
		if(cr[n]*NW>maxrho) {
			maxrho=cr[n]*NW;
			*dd=n;
		}
	S0=0; S1=0; S2=0; S3=0; S4=0; R0=0; R1=0; R2=0;
	for(k=*dd-dn;k<=*dd+dn;k++) {
		K=k; if(k<0) K+=NW; if(k>=NW) K-=NW; 
		S0++; S1+=1.*k; S2+=1.*k*k; S3+=1.*k*k*k; S4+=1.*k*k*k*k; R0+=cr[K]*NW; R1+=1.*k*cr[K]*NW; R2+=1.*k*k*cr[K]*NW;
	}

	a=((R0*S1-R1*S0)*(S0*S3-S1*S2)-(R0*S2-R2*S0)*(S0*S2-S1*S1))/((S1*S2-S0*S3)*(S0*S3-S1*S2)-(S2*S2-S0*S4)*(S0*S2-S1*S1));
	b=(a*(S1*S2-S0*S3)-R0*S1+R1*S0)/(S0*S2-S1*S1);
	c=(R0-a*S2-b*S1)/S0;
	*rho=-b*b/(4*a)+c; 
	tmp=-b/(2*a);
	if(tmp>=*dd-dn & tmp<*dd+dn) *dd=tmp; 
	
	*sigma=0;
}

void compute_coherence(ar,ai,br,bi,cr,ci,apo,f,NW,rho,dd,sigma)
float *ar,*ai,*br,*bi,*cr,*ci,*apo,*rho,*dd,*sigma,*f;
int NW;
{
	float S1,S2,S3,S4,S5,S6,S7,var_eps,var_tau,delta_tau,tmp1,tmp2,*phi;
	int n,count,n1,n2,k;

	phi=(float *)calloc(NW,sizeof(float));

	for(n=0;n<NW;n++) {
		ar[n]*=apo[n];
		br[n]*=apo[n];
	}

	FFT(1,PW,ar,ai);
	FFT(1,PW,br,bi);
	S1=0; S2=0; S3=0; S4=0; S5=0; S6=0; S7=0; count=0; *rho=0;
	for(n=0;n<NW/2+1;n++) { 
		n1=n-dn; n2=n+dn; if(n1<0) { n1=0; n2=2*dn; } if(n2>=NW) { n1=NW-1-2*dn; n2=NW-1; }
		cr[n]=0; ci[n]=0; tmp1=0; tmp2=0; 
		for(k=n1;k<=n2;k++) {
			cr[n]+=ar[k]*br[k]+ai[k]*bi[k]; 
			ci[n]+=ai[k]*br[k]-ar[k]*bi[k];
			tmp1+=ar[k]*ar[k]+ai[k]*ai[k];
			tmp2+=br[k]*br[k]+bi[k]*bi[k];
		}
		if(tmp1*tmp2) {
			cr[n]/=sqrt(tmp1*tmp2);
			ci[n]/=sqrt(tmp1*tmp2);
		} else { cr[n]=0.001; ci[n]=0.001; }
		phi[n]=atan2(ci[n],cr[n]);	// phase
		if(n>0) {					// unwraping
			while(phi[n]-phi[n-1]>PI) phi[n]-=2*PI;
			while(phi[n]-phi[n-1]<-PI) phi[n]+=2*PI;
		}
		cr[n]=sqrt(cr[n]*cr[n]+ci[n]*ci[n]);
		if(f[n]>=f1 & f[n]<=f2) {
			S1+=(2*PI*f[n])*(2*PI*f[n])*cr[n]*cr[n];
			S2+=2*PI*f[n]*cr[n]*cr[n];
			S3+=2*PI*f[n]*phi[n]*cr[n]*cr[n];
			S4+=cr[n]*cr[n];
			S5+=phi[n]*cr[n]*cr[n];
			S6+=phi[n]*phi[n]*cr[n]*cr[n];
			*rho+=cr[n];
			count++;
		}
	}
	for(n=0;n<NW/2+1;n++)
		if(f[n]>=f1 & f[n]<=f2)
			S7+=(2*PI*f[n]-S2/S4)*(2*PI*f[n]-S2/S4)*cr[n]*cr[n]*cr[n]*cr[n];
	*dd=(S3*S4-S2*S5)/(S1*S4-S2*S2)*FACQ;
	
	*rho/=count;	
	var_eps=(S6*S4-S5*S5)/(S4*S4)-(S3*S4-S2*S5)*(S3*S4-S2*S5)/(S4*S4*(S1*S4-S2*S2));
	*sigma=sqrt(var_eps*S7*S4*S4/((S1*S4-S2*S2)*(S1*S4-S2*S2)))*FACQ;

	free(phi);
}	


void read_data(rep,name,i,s,S)
char rep[100],name[100];
int i,s;
float S[];
{
	char nametot[100],*line=NULL;
	FILE *in;
	int n;
	size_t len=0;
    printf(".");
	sprintf(nametot,"%s/%s%d_%d.txt",rep,name,s+1,i+1); 
    //printf("Lecture : %s%d_%d.txt\n",name,s+1,i+1);
    float a;
    in=fopen(nametot,"r");
    printf(".");
	for(n=0;n<NHEADER;n++)  GETL;	// header
	for(n=0;n<NSAMPLES;n++) 
        fscanf(in,"%*f, %f",&S[n]);
	fclose(in);	
}
	



void doublet(rep,name,i,j,rho,tau,dtau,freq,ramp,method)	// modifié dans cette version 
char rep[100],name[100];
float *rho,*tau,*dtau,*freq,*ramp;
int method,i,j;
{
	FILE *in;
	int n,s,d,k,kmax,nfen,iter,maxiter=10,NW;
	float *f,*but,*han,*ar,*ai,*br,*bi,*cr,*ci,stdA,stdB,maxrho,*dd,*RHO,D,*SIGMA,var;
	float *tau_tmp,*dtau_tmp,*rho_tmp,*ramp_tmp,rho_max,f1b,ma,mb,*tmp,*A,*B;
	char nameA[100],nameB[100];

	dd=(float *)calloc(1,sizeof(float));
	RHO=(float *)calloc(1,sizeof(float));
	SIGMA=(float *)calloc(1,sizeof(float));

	nfen=1+flor(0.5*FACQ/(gf*df)-F1/df);
	rho_tmp=(float *)calloc(nfen,sizeof(float));
	tau_tmp=(float *)calloc(nfen,sizeof(float));
	dtau_tmp=(float *)calloc(nfen,sizeof(float));
	ramp_tmp=(float *)calloc(nfen,sizeof(float));
	tmp=(float *)calloc(1,sizeof(float));

	A=(float *)calloc(NSAMPLES,sizeof(float));
	B=(float *)calloc(NSAMPLES,sizeof(float));
		
	// frequencies and taper window
	NW=(int)round(exp(PW*log(2.))); 
	but=(float *)calloc(NW,sizeof(float));
	han=(float *)calloc(NW,sizeof(float));
	f=(float *)calloc(NW,sizeof(float));
	for(n=0;n<NW;n++) {
		if(n<=NW*0.5) f[n]=n*FACQ/NW; else f[n]=(NW-n)*FACQ/NW;
		han[n]=0.5-0.5*cos(2.*PI*n/NW); 
	}

	// processing
	ar=(float *)calloc(NW,sizeof(float));
	ai=(float *)calloc(NW,sizeof(float));
	br=(float *)calloc(NW,sizeof(float));
	bi=(float *)calloc(NW,sizeof(float));
	cr=(float *)calloc(NW,sizeof(float));	
	ci=(float *)calloc(NW,sizeof(float));

	for(s=0;s<NST;s++) {
		read_data(rep,name,i,s,A);
		read_data(rep,name,j,s,B);
		for(k=0,rho_max=0;k<nfen;k++) {
            f1=F1+k*df; f2=f1*gf; 
			if(f1==0) f1b=f[1]*1e-6; else f1b=f1;
			for(n=0;n<NW;n++) // butherworth filter (band-pass)
				but[n]=sqrt(1./(1.+exp(2.*no*log(f[n]/f2))))*(1-sqrt(1./(1.+exp(2.*no*log(f[n]/f1b)))));	// NB : but=0 for f=0			
			D=0; iter=0; var=0;
			
            while(iter<maxiter) {
				d=rint(D);
				for(n=0,ma=0,mb=0;n<NW;n++) { 
					if(d>=0) { ar[n]=A[n]; br[n]=B[n+d]; }
					else { ar[n]=A[n-d]; br[n]=B[n]; }
					ai[n]=0; bi[n]=0;
					ma+=ar[n]; mb+=br[n]; 
				}	
				for(n=0;n<NW;n++) {	// centering
					ar[n]-=(ma/NW); 
					br[n]-=(mb/NW);
				}
				if(method==1) compute_coherence(ar,ai,br,bi,cr,ci,han,f,NW,RHO,dd,SIGMA);
				if(method==2) compute_correlation(ar,ai,br,bi,cr,ci,han,but,f,NW,RHO,dd,SIGMA,tmp);
				ramp_tmp[k]=*tmp;

				D+=*dd; if(D>=NW/2+1) D-=NW;
				var+=*SIGMA*(*SIGMA);				

				if(rint(D)==d) break; 	// modification 10/7/2015
				iter++; 
			}
			rho_tmp[k]=*RHO;
			tau_tmp[k]=D;
			dtau_tmp[k]=sqrt(var);
			if(rho_tmp[k]>rho_max) { rho_max=rho_tmp[k]; kmax=k; }
		}
		rho[s]=rho_tmp[kmax];
		tau[s]=tau_tmp[kmax]; 
		dtau[s]=dtau_tmp[kmax];
		freq[s]=F1+kmax*df;
		ramp[s]=ramp_tmp[kmax];
	}
		
	free(but); free(han); free(f); free(ar); free(ai); free(br); free(bi); free(cr); free(ci); free(A); free(B);  		
}


void main(argc,argv)	// modifié dans cette version 
int argc;
char *argv[];
{
	int n,N,i,j,method,essai,eprouvette;
	float *rho1,*tau1,*dtau1,*rho2,*tau2,*dtau2,*freq,*freq_tmp,*ramp;
	char name[1000],rep[1000],nameout[1400],namein[100],**nom=NULL,*line=NULL,tmp[100],mat[100],brute[100],traitement[100],ty[100];
	FILE *in,*out;
	size_t len=0;

	sscanf(argv[1],"%s",namein); 
	in=fopen(namein,"r");
    GETL; sscanf(line,"%s",ty);
    printf("%s\n",ty);
	GETL; sscanf(line,"%s",mat);
    printf("%s\n",mat);
    GETL; sscanf(line,"%d",&eprouvette);
    printf("%d\n",eprouvette);
	GETL; sscanf(line,"%d",&essai);
    printf("%d\n",essai);
	GETL; sscanf(line,"%s",brute);
    printf("%s\n",brute);
	GETL; sscanf(line,"%s",traitement);
    printf("%s\n",traitement);
    
    // Ancienne version
    //GETL; sscanf(line,"%s",name);
    //printf("%s\n",name);
	//GETL; sscanf(line,"%s",rep);
    //printf("%s\n",rep);
	//GETL; sscanf(line,"%s",nameout);
    //printf("%s\n",nameout);
	GETL; sscanf(line,"%d",&NHEADER);
	GETL; sscanf(line,"%d",&method);
	GETL; sscanf(line,"%d",&NSAMPLES);
    printf("%d\n",NSAMPLES);
	GETL; sscanf(line,"%d",&PW);
	GETL; sscanf(line,"%f",&F1);	
	GETL; sscanf(line,"%f",&df);	
	GETL; sscanf(line,"%f",&gf);	
	GETL; sscanf(line,"%d",&dn);
	GETL; sscanf(line,"%f",&thresh);
	GETL; sscanf(line,"%d",&N); 
	GETL; sscanf(line,"%d",&NST); 

    // Constitution des chemins d'accès complets à partir des racines
    sprintf(name,"%s_%s_%d.%d_",ty,mat,eprouvette,essai);
    printf("%s\n",name);
    sprintf(rep,"%s/%s/%s/%d.%d/EA/waveforms",brute,ty,mat,eprouvette,essai);
    printf("%s\n",rep);
    sprintf(nameout,"%s/%s/%s/%scohcor.txt",traitement,ty,mat,name); 
    printf("%s\n",nameout);
    
    
	// main loop
	rho1=(float *)calloc(NST,sizeof(float));
	tau1=(float *)calloc(NST,sizeof(float));	
	dtau1=(float *)calloc(NST,sizeof(float));	
	rho2=(float *)calloc(NST,sizeof(float));
	tau2=(float *)calloc(NST,sizeof(float));	
	dtau2=(float *)calloc(NST,sizeof(float));	
	freq=(float *)calloc(NST,sizeof(float));	
	freq_tmp=(float *)calloc(NST,sizeof(float));
	ramp=(float *)calloc(NST,sizeof(float));
    
	out=fopen(nameout,"w");
    fprintf(out,"Calcul de corrélation et cohérence de l'essai %s\n\n",name);
    fprintf(out," Ev1 Ev2 Ch Coh      DTcoh       iDTcoh       f1coh     Cor      DTcor       f1cor     rEv1Ev2\n");
	for(i=0;i<N-1;i++) {		
		printf("%d / %d\n",i+1,N);
        printf(".");
		for(j=i+1;j<N;j++) {
			if(method==1) {		// just coherency
				doublet(rep,name,i,j,rho1,tau1,dtau1,freq,ramp,1);
				for(n=0;n<NST;n++) 
					if(rho1[n]>thresh) 
						fprintf(out,"    %d %d %d %f %e %e %f %f\n",i+1,j+1,n+1,rho1[n],tau1[n],dtau1[n],freq[n],ramp[n]);
			}
			if(method==2) {		// just correlation
				doublet(rep,name,i,j,rho2,tau2,dtau2,freq,ramp,2);
				for(n=0;n<NST;n++) 
					if(rho2[n]>thresh) 
						fprintf(out,"    %d %d %d %f %e %f %f\n",i+1,j+1,n+1,rho2[n],tau2[n],freq[n],ramp[n]);
			}
			if(method==3) {		// both coherency + correlation
                doublet(rep,name,i,j,rho1,tau1,dtau1,freq,ramp,1); 
                for(n=0;n<NST;n++) freq_tmp[n]=freq[n];
				doublet(rep,name,i,j,rho2,tau2,dtau2,freq,ramp,2);
				for(n=0;n<NST;n++) 
					if(rho1[n]>thresh) 
						fprintf(out,"    %d %d %d %f %e %e %f %f %e %f %f\n",i+1,j+1,n+1,rho1[n],tau1[n],dtau1[n],freq_tmp[n],rho2[n],tau2[n],freq[n],ramp[n]);
			}
		}
	}
	fclose(out);
    fprintf(stdout, "\aBeep!\n" );
    int beep(void);
}
