int main1(int a,int b,int p){
  int l, i, v, y;

  l=57;
  i=0;
  v=a;
  y=b;

  
  /*@

    loop invariant v == a + b*i;

    loop invariant y == b - i;

    loop invariant 0 <= i <= l;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant p == \at(p, Pre);

    loop assigns v, y, i;

  */
  while (i<l) {
      v = v+1;
      y = y-1;
      v = v+y;
      v = v+i;
      i = i+1;
  }

}