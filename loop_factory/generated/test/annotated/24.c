int main1(int k,int g){
  int phg, r5c, qi;
  phg=0;
  r5c=(g%20)+5;
  qi=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r5c <= ((\at(g,Pre) % 20) + 5);
  loop invariant k == \at(k,Pre) + 2 * ( ((\at(g,Pre) % 20) + 5) - r5c );
  loop invariant phg == 0;
  loop invariant k + 2*r5c == \at(k, Pre) + 2*( (\at(g, Pre) % 20) + 5 );
  loop invariant qi == 3;
  loop invariant g >= \at(g, Pre);
  loop invariant r5c == ((\at(g,Pre) % 20) + 5) - ((k - \at(k,Pre)) / 2);
  loop invariant k >= \at(k,Pre);
  loop invariant g == \at(g, Pre) + (((\at(g, Pre) % 20) + 5 - r5c) * ((\at(g, Pre) % 20) + 5)) - ((((\at(g, Pre) % 20) + 5 - r5c) * ((\at(g, Pre) % 20) + 5 - r5c + 1)) / 2);
  loop assigns r5c, qi, k, g;
*/
while (1) {
      if (!(r5c>0)) {
          break;
      }
      r5c = r5c - 1;
      qi = qi + phg;
      k += 2;
      g += r5c;
  }
}