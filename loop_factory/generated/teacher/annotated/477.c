int main1(int a,int b){
  int w, k, r;

  w=8;
  k=0;
  r=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == 8;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant r >= 8;
  loop invariant (r - 8) % 10 == 0;
  loop invariant r % 10 == 8;
  loop invariant ((r - 8) % 10) == 0;
  loop assigns r;
*/
while (1) {
      r = r+4;
      r = r+6;
  }

}
