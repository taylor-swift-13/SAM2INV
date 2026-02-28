int main125(int a,int b,int n){
  int l, q, d, j, e;

  l=a;
  q=0;
  d=q;
  j=-5;
  e=a;

  while (d!=0&&j!=0) {
      if (d>j) {
          d = d-j;
      }
      else {
          j = j-d;
      }
  }

  while (q-e>0) {
      d = d+l;
      l = l*4+3;
      d = d*l+3;
      if (d+1<e) {
          l = l*l+d;
      }
  }


  /*@ assert q-e <= 0; */
}
