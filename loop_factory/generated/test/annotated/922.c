int main1(int h){
  int zkx, k, t2, ab2;
  zkx=h+23;
  k=2;
  t2=1;
  ab2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zkx == \at(h, Pre) + 23;
  loop invariant k == 2;
  loop invariant ab2 >= 0;
  loop invariant t2 >= 1;
  loop invariant h == \at(h, Pre) + ab2 * k;
  loop assigns h, ab2, t2;
*/
while (t2<=zkx) {
      h = h + k;
      ab2 += 1;
      t2 = 2*t2;
  }
}