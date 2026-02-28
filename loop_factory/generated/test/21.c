int main21(int a,int p,int q){
  int g, k, s;

  g=a+5;
  k=g+4;
  s=q;

  while (k>=g+1) {
      s = s*2;
      s = s*s+s;
      k = k-3;
  }

  while (s-1>=0) {
      k = k+4;
      k = k+s;
      s = s-1;
  }


  /*@ assert s-1 < 0; */
}
