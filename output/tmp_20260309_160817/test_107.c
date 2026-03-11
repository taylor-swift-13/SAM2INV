int main1(int a){
  int k, i, qv;
  k=0;
  i=(a%20)+10;
  qv=(a%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k >= 0;
  loop invariant i <= ((\at(a, Pre) % 20) + 10);
  loop invariant qv <= ((\at(a, Pre) % 15) + 8);
  loop invariant i + qv + k == ((\at(a, Pre) % 20) + (\at(a, Pre) % 15) + 18);
  loop invariant (i + qv) == (a % 20) + (a % 15) + 18 - k;
  loop invariant i <= (a % 20) + 10;
  loop invariant qv <= (a % 15) + 8;
  loop invariant i - qv == ((\at(a,Pre) % 20) + 10) - ((\at(a,Pre) % 15) + 8) - (k % 2);
  loop assigns i, qv, k;
*/
for (; i>0&&qv>0; k += 1) {
      if (k%2==0) {
          i--;
      }
      else {
          qv--;
      }
  }
/*@
  assert k >= 0;
  assert (i <= 0 || qv <= 0);
  assert i == ((\at(a, Pre) % 20) + 10) - (k + 1) / 2;
  assert qv == ((\at(a, Pre) % 15) + 8) - k / 2;
*/
}
