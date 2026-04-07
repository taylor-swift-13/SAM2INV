int main1(){
  int t0, v8n, h8k, wp5p, z;
  t0=(1%39)+10;
  v8n=0;
  h8k=12;
  wp5p=0;
  z=t0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (v8n == 0 || v8n == t0);
  loop invariant (v8n == 0 ==> (z == t0 && wp5p == 0));
  loop invariant (v8n == t0 ==> wp5p == z);
  loop invariant 0 <= v8n;
  loop invariant v8n <= t0;
  loop invariant z == t0;
  loop assigns z, wp5p, v8n;
*/
while (v8n < t0) {
      z = (z*(1)+(-((v8n % 2)) + h8k*(v8n % 2)));
      wp5p = z*(1 - (v8n % 2)) + wp5p*(v8n % 2);
      v8n = t0;
  }
}