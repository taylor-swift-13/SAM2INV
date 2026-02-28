int main62(int a,int m,int q){
  int k, b, p, r;

  k=m+24;
  b=0;
  p=-1;
  r=2;

  while (b<k) {
      r = r+p;
      p = p+r+r;
      p = p+1;
  }


  /*@ assert b >= k; */
}
