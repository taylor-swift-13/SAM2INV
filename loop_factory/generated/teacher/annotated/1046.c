int main1(int a,int p){
  int s, c, y, v;

  s=(p%24)+16;
  c=0;
  y=p;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant s == (\at(p, Pre) % 24) + 16;
  loop invariant c == 0;
  loop invariant (y - \at(p, Pre)) % 4 == 0;
  loop invariant y >= \at(p, Pre);
  loop invariant (y - \at(p, Pre)) % 4 == 0 && y >= \at(p, Pre) && c == 0;
  loop invariant p == \at(p, Pre) && a == \at(a, Pre) && s == \at(p, Pre) % 24 + 16;
  loop invariant a == \at(a, Pre);
  loop invariant (p == \at(p, Pre)) && (a == \at(a, Pre)) && (c == 0);
  loop invariant s == \at(p, Pre) % 24 + 16;

  loop invariant (y - \at(p, Pre)) % 4 == 0 && y >= \at(p, Pre);
  loop invariant c == 0 && p == \at(p, Pre) && s == \at(p, Pre) % 24 + 16 && a == \at(a, Pre);
  loop assigns y;
*/
while (1) {
      y = y+4;
      c = c;
  }

}
