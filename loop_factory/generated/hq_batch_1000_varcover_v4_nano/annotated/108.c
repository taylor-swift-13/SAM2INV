int main1(int b,int m,int p){
  int l, i, v, y;

  l=40;
  i=l;
  v=b;
  y=l;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant y == i;

    loop invariant v + i == b + l;

    loop assigns i, v, y;

    loop variant i;

  */
  while (i>0) {
      v = v+1;
      y = y-1;
      i = i-1;
  }

}