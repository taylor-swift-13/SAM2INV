int main1(int k){
  int cz1, wkz, o, l, e9;
  cz1=k+24;
  wkz=0;
  o=-4;
  l=wkz;
  e9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cz1 == k + 24;
  loop invariant l == 0;
  loop invariant e9 == 0;
  loop invariant (o + 4) % 3 == 0;
  loop invariant o >= -4;
  loop invariant wkz <= 0;
  loop assigns wkz, l, o, e9;
*/
while (1) {
      if (!(wkz > cz1 && (o > k || l > k || e9 > k))) {
          break;
      }
      wkz = wkz-((o>k)+(l>k)+(e9>k));
      l += l;
      o = o + 3;
      e9 += l;
  }
}