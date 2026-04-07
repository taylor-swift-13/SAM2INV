int main1(int k){
  int sju, i6p, za, at;
  sju=k;
  i6p=0;
  za=0;
  at=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sju == \at(k, Pre);
  loop invariant (i6p == 0 || i6p == sju);
  loop invariant (i6p == 0 ==> at == 1) && (i6p != 0 ==> at == k);
  loop invariant (i6p == 0 ==> za == 0) && (i6p != 0 ==> za == at);
  loop invariant i6p >= 0;
  loop invariant (i6p == 0 || (sju > 0 && i6p == sju));
  loop assigns at, i6p, za;
*/
while (i6p < sju && (at *= k, i6p++, 1)) {
      za = za + at;
      i6p = sju;
  }
}