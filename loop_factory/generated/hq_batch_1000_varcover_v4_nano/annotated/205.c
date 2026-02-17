int main1(int b,int k,int q){
  int l, i, v, j;

  l=22;
  i=0;
  v=0;
  j=b;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant v == 2*j*i;

    loop invariant j == b;

    loop invariant l == 22;

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v+j+j;
      i = i+1;
  }

}