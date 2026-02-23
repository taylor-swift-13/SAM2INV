int main1(int b,int q){
  int l, k, v;

  l=49;
  k=l;
  v=l;

  while (k>=1) {
      v = v*v+v;
      if (q*q<=l+2) {
          v = v*v;
      }
      k = k-1;
  }

}
