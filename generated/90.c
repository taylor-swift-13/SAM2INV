int main90(int s,int n){
  int gx, nlw, k, wvn, reys, qng, we;

  gx=n+23;
  nlw=gx+3;
  k=gx;
  wvn=0;
  reys=n*4;
  qng=nlw;
  we=0;

  while (k<gx) {
      k = k + 7;
      qng = qng + k;
      reys += 2;
      we = we + nlw;
      wvn = wvn+(k%7);
      wvn = wvn*2;
  }

}
