int main1(){
  int k, klq, za, rv;
  k=1+5;
  klq=3;
  za=k - klq;
  rv=klq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (klq == k) || (klq < k && za == k - klq && rv == klq);
  loop invariant 0 <= klq;
  loop invariant 0 <= za;
  loop invariant za <= k;
  loop assigns za, rv, klq;
*/
while (klq < k) {
      za = (k)+(-((++klq)));
      rv += klq;
      klq = k;
  }
}