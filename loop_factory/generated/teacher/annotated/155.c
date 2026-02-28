int main1(int m){
  int i, g, o, x;

  i=20;
  g=i;
  o=g;
  x=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 3*o + 4*g == 140;
  loop invariant 9*(x - 1) == 2*g*g - 146*g + 2120;
  loop invariant g >= 2;
  loop invariant g <= 20;
  loop invariant m == \at(m, Pre);
  loop invariant o % 4 == 0;
  loop invariant g % 3 == 2;
  loop invariant i == 20;
  loop invariant o >= 20;
  loop invariant 8*(x-1) == (o-20)*(o+24);
  loop invariant 3*(o - 20) == 4*(20 - g);
  loop invariant 9*x == 9 + 66*(20 - g) + 2*(20 - g)*(20 - g);
  loop invariant (g - 2) % 3 == 0;
  loop assigns o, x, g;
*/
while (g>2) {
      o = o+4;
      x = x+o;
      g = g-3;
  }

}
