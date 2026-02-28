int main30(int b,int n,int p){
  int l, k, u, e;

  l=n+9;
  k=0;
  u=n;
  e=4;

  while (k<=l-1) {
      u = u+3;
      u = u+e+e;
      e = e+k;
  }


  /*@ assert k > l-1; */
}
