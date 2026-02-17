int main1(int b,int k,int q){
  int l, i, v, c, y;

  l=68;
  i=0;
  v=b;
  c=k;
  y=-3;

  
  /*@

    loop invariant v == b + 3*i;

    loop invariant y == -3 + 4*i;

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant q == \at(q, Pre);

    loop assigns v, y, i;

  */
  while (i<l) {
      v = v+3;
      y = y+4;
      i = i+1;
  }

}