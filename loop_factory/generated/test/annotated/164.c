int main1(int a,int b,int n,int p){
  int l, i, v, t;

  l=a+11;
  i=0;
  v=i;
  t=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a,Pre);
    loop invariant b == \at(b,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant p == \at(p,Pre);
    loop invariant l == a + 11;
    loop invariant v >= 0;
    loop invariant i == 0;
    loop invariant t == \at(b,Pre) || t == l;
    loop invariant (\at(b,Pre) ==> v == 0);
    loop invariant v == 0 || t == l;
    loop invariant l == \at(a, Pre) + 11;
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop assigns v, t;
  */
while (v!=0&&t!=0) {
      if (v>t) {
          v = v-t;
      }
      else {
          t = t-v;
      }
      v = v+1;
      t = t-1;
      t = v-t;
      v = v+i;
      t = l;
      v = v+5;
  }

}