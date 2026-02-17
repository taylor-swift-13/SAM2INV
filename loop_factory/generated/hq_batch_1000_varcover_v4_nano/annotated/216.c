int main1(int b,int m,int p){
  int l, i, v, t;

  l=63;
  i=0;
  v=-4;
  t=m;

  /* >>> LOOP INVARIANTS TO FILL <<< */
    /*@
    loop invariant 4*v - 5*t == -16 - 5*m;
    loop invariant l == 63;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant m == \at(m, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant p == \at(p, Pre);
    loop assigns v, t;
  */
  while (i<l) {
      v = v+1;
      t = t+1;
      v = v+4;
      t = t+3;
  }

}