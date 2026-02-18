int main1(int a,int k,int m,int p){
  int l, i, v, w;

  l=52;
  i=l;
  v=5;
  w=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i + v == 57;
    loop invariant w == 3 + (52 - i) * 7 + (52 - i) * (51 - i) / 2;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && p == \at(p, Pre);
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant l == 52;
    loop invariant v == 57 - i;
    loop invariant 2*w == v*v + 3*v - 34;
    loop invariant v + i == 57;
    loop invariant 0 <= i <= 52;
    loop invariant 5 <= v <= 57;
    loop invariant 3 <= w <= 1693;
    loop invariant w == (i*i - 117*i + 3386)/2;
    loop assigns v, w, i;
  */
  while (i>0) {
      v = v+1;
      w = w+v;
      w = w+1;
      i = i-1;
  }

}