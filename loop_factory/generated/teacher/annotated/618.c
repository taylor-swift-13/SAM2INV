int main1(int b,int k){
  int h, a, p, f, c, w;

  h=k+10;
  a=0;
  p=5;
  f=2;
  c=-1;
  w=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant h == \at(k, Pre) + 10;
  loop invariant f >= 2;
  loop invariant (f - 2) % p == 0;
  loop invariant h == k + 10;
  loop invariant ( (f - 2) % p == 0 );
  loop invariant (f >= 2);
  loop invariant p > 0;
  loop invariant (f - 2) % 5 == 0;
  loop assigns f;
*/
while (1) {
      f = f+p;
  }

}
