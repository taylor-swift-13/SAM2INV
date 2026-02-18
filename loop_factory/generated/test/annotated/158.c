int main1(int a,int b,int n,int p){
  int l, i, v, f, t;

  l=68;
  i=0;
  v=3;
  f=8;
  t=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 3 + i;
    loop invariant f == i*i + 3*i + 8;
    loop invariant (i % 2 == 0) ==> (t == p + i/2);
    loop invariant (i % 2 == 1) ==> (t == 4 - p + i/2);
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant 0 <= i <= l;
    loop invariant v == i + 3;
    loop invariant f == 8 + i*i + 3*i;
    loop invariant p == \at(p, Pre);
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);

    loop invariant (i % 2 == 1) ==> (t == i/2 + 4 - \at(p, Pre));
    loop invariant l == 68;
    loop invariant (i % 2 != 0) ==> (t == -p + 4 + i/2);
    loop assigns v, f, t, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      f = f+v;
      f = f+i;
      t = v-t;
      i = i+1;
  }

}