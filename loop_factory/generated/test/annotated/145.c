int main1(int a,int b,int n,int p){
  int l, i, v;

  l=37;
  i=l;
  v=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 37;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant (i == l) ==> (v == 6);
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant v == 6 || v == 0;
    loop invariant i <= 37;
    loop invariant (i == 37) ==> (v == 6);
    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && n == \at(n, Pre) && p == \at(p, Pre);
    loop invariant 0 <= i && i <= l;

    loop assigns i, v;
    loop variant i;
  */
while (i>0) {
      v = v-v;
      v = v+v;
      i = i-1;
  }

}