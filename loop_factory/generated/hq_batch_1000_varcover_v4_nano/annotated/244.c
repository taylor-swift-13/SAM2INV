int main1(int a,int m,int p){
  int l, i, v;

  l=43;
  i=0;
  v=m;

  
  /*@

    loop invariant v == m + i*(i+1);

    loop invariant 0 <= i && i <= l;

    loop invariant m == \at(m, Pre);

    loop invariant l == 43;

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+2;
      v = v+i;
      v = v+i;
      i = i+1;
  }

}