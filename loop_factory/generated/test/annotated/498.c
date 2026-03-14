int main1(int h,int v){
  int ee9, my, spy, lx7, o, sx, iti;
  ee9=v;
  my=ee9;
  spy=0;
  lx7=(h%28)+10;
  o=-6;
  sx=8;
  iti=my;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iti == my*(spy+1);
  loop invariant o == -6 + my*spy;
  loop invariant lx7 == ((\at(h, Pre) % 28) + 10) - spy*(spy-1)/2;
  loop invariant v >= \at(v, Pre);
  loop invariant lx7 == (h % 28) + 10 - ((spy * (spy - 1)) / 2);
  loop invariant spy >= 0;
  loop assigns lx7, iti, spy, o, v;
*/
while (lx7>spy) {
      lx7 -= spy;
      iti += my;
      spy = spy + 1;
      o += my;
      v = v+(spy%3);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (h - \at(h, Pre)) % 8 == 0;
  loop invariant spy >= 0;
  loop invariant h >= \at(h, Pre);
  loop assigns spy, h, iti, o, lx7;
*/
while (spy>o) {
      spy = spy - o;
      h = h + sx;
      iti = iti*4+3;
      o = o + 1;
      lx7 = lx7*iti+3;
  }
}