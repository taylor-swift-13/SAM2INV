int main1(int a,int p){
  int r, i, v, f, c, e;

  r=a+9;
  i=0;
  v=r;
  f=3;
  c=i;
  e=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == a + 9;
  loop invariant i == 0;
  loop invariant v >= r;
  loop invariant ((v - r) % 3 == 0);
  loop invariant (v - r) % 3 == 0;
  loop invariant a == \at(a,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant v >= a + 9;
  loop invariant ((3 + i) != 0) ==> ((v - (a + 9)) % (3 + i) == 0);
  loop assigns v;
*/
while (1) {
      v = v+3;
      v = v+i;
  }

}
