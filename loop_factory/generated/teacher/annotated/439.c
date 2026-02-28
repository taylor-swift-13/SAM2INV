int main1(int a,int b){
  int t, w, x;

  t=24;
  w=1;
  x=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (a == \at(a, Pre));
  loop invariant (b == \at(b, Pre));
  loop invariant (t == 24);
  loop invariant ((x + 8) % 9 == 0);
  loop invariant (x >= 1);
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant t == 24;
  loop invariant x >= 1;
  loop invariant x == 1 || (x >= 10 && x % 2 == 0);
  loop invariant (x + 8) % 9 == 0;
  loop assigns x;
*/
while (1) {
      x = x+4;
      x = x+x;
  }

}
