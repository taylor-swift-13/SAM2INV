int main1(int i){
  int hfw5, tt4, b, s, t4u;
  hfw5=i*5;
  tt4=hfw5;
  b=tt4;
  s=0;
  t4u=i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hfw5 == 5 * \at(i, Pre);
  loop invariant (tt4 - hfw5) >= 0;
  loop invariant i == (\at(i, Pre) - ((tt4 - hfw5) * ((tt4 - hfw5) - 1)) / 2);
  loop invariant b == (hfw5 * ((tt4 - hfw5) + 1) + ((tt4 - hfw5) * ((tt4 - hfw5) - 1)) / 2);
  loop assigns s, b, i, tt4;
*/
while (tt4-1>=0) {
      s += b;
      b += tt4;
      i = i+hfw5-tt4;
      tt4 += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hfw5 == (\at(i, Pre) * 5);
  loop invariant t4u >= \at(i, Pre);
  loop assigns s, t4u, tt4, i;
*/
while (t4u<=b-1) {
      s = s + i;
      t4u = t4u + 1;
      tt4 = tt4*2;
      i = i + s;
  }
}