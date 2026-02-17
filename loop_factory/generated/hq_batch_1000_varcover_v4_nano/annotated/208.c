int main1(int a,int k,int m){
  int l, i, v, y, e, t, n, w, g;

  l=66;
  i=0;
  v=-6;
  y=k;
  e=k;
  t=m;
  n=5;
  w=-2;
  g=m;

  
  /*@

    loop invariant i % 5 == 0;

    loop invariant 0 <= i && i <= l + 4;

    loop invariant (i == 0) ==> (v == -6 && y == k);

    loop invariant (i == 0 || v % 4 == 0);

    loop invariant k == \at(k,Pre) && m == \at(m,Pre) && a == \at(a,Pre);

    loop assigns v, y, i;

    loop variant l + 4 - i;

  */
while (i<l) {
      v = v*4;
      y = y/4;
      y = y*2;
      i = i+5;
  }

}