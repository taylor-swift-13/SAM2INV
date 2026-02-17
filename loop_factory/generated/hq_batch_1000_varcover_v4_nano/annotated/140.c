int main1(int b,int m,int p){
  int l, i, v;

  l=(b%6)+15;
  i=0;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == (b % 6) + 15;
    loop invariant 0 <= i && i <= l;
    loop invariant (i == 0) ==> (v == m);
    loop invariant (i > 0) ==> (v == 2*(i - 1));
    loop invariant b == \at(b, Pre) && m == \at(m, Pre) && p == \at(p, Pre);
    loop assigns v, i;
    loop variant l - i;
  */
while (i<l) {
      v = v+1;
      v = v-v;
      v = v-v;
      v = v+i;
      v = v+i;
      i = i+1;
  }

}