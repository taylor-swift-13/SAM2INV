int main1(int d,int t){
  int l, ieg, dj6, aj, x, et, blu, e6, l1f, avf;
  l=t+20;
  ieg=0;
  dj6=0;
  aj=0;
  x=0;
  et=d;
  blu=5;
  e6=0;
  l1f=l;
  avf=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (aj + 4 * dj6) == ieg;
  loop invariant dj6 == ieg / 4;
  loop invariant x == ieg;
  loop invariant et == d + ieg;
  loop invariant l1f == l + 2 * ieg;
  loop invariant avf == d + (ieg * (ieg + 3)) / 2;
  loop invariant blu == 5 + ieg * d + (ieg * (ieg + 1)) / 2;
  loop invariant e6 == 8 * (ieg / 2);
  loop invariant 0 <= ieg && (l >= 0 ==> ieg <= l);
  loop invariant et == \at(d,Pre) + ieg;
  loop invariant l == \at(t,Pre) + 20;
  loop invariant avf == (\at(d, Pre) + (ieg * (ieg + 3)) / 2);
  loop invariant blu == (5 + ieg * \at(d, Pre) + (ieg * (ieg + 1)) / 2);
  loop invariant (0 <= aj && aj < 4);
  loop invariant (0 <= dj6 && dj6 <= ieg);
  loop invariant aj == ieg % 4;
  loop assigns aj, x, dj6, ieg, e6, et, l1f, avf, blu;
*/
while (1) {
      if (!(ieg<l)) {
          break;
      }
      aj += 1;
      x = x + 1;
      if (aj>=4) {
          aj -= 4;
          dj6 += 1;
      }
      ieg = ieg + 1;
      if ((ieg%2)==0) {
          e6 = e6-(-8);
      }
      et++;
      l1f += 2;
      avf += x;
      blu = blu + et;
      avf += 1;
  }
}