int main1(int b,int p){
  int h, d, v, y;

  h=(b%35)+6;
  d=0;
  v=b;
  y=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - y == 4 || (v == \at(b, Pre) && y == \at(p, Pre));
  loop invariant v >= \at(b, Pre);
  loop invariant h == \at(b, Pre) % 35 + 6;
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);

  loop invariant (y == \at(p, Pre) && v == \at(b, Pre)) || v - y == 4;
  loop invariant b == \at(b, Pre) && p == \at(p, Pre);
  loop invariant h == (\at(b, Pre) % 35 + 6);
  loop invariant (v == \at(b, Pre) && y == \at(p, Pre)) || (v - y == 4);
  loop invariant (v - \at(b, Pre)) % 4 == 0;
  loop invariant ((y == \at(p, Pre) && v == \at(b, Pre)) || v == y + 4) && v >= \at(b, Pre);
  loop invariant b == \at(b, Pre) && p == \at(p, Pre) && h == (\at(b, Pre) % 35) + 6;
  loop invariant h == (\at(b, Pre) % 35) + 6;
  loop invariant y == \at(p, Pre) || ((y - \at(b, Pre)) % 4 == 0);
  loop invariant b == \at(b,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant h == \at(b,Pre) % 35 + 6;
  loop invariant (v - \at(b,Pre)) % 4 == 0;
  loop invariant v >= \at(b,Pre);
  loop invariant (v - y == 4) || (v == \at(b, Pre) && y == \at(p, Pre));
  loop assigns v, y;
*/
while (1) {
      y = v;
      v = v+3;
      v = v+1;
  }

}
