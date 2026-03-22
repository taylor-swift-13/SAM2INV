int main1(int d){
  int hc, q, iv, w;
  hc=d;
  q=(d%40)+2;
  iv=0;
  w=hc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == hc + (q - ((\at(d, Pre) % 40) + 2));
  loop invariant hc == \at(d,Pre);
  loop invariant hc == d;
  loop assigns iv, q, w;
*/
while (q!=iv) {
      iv = q;
      q = (q+hc/q)/2;
      w = w+q-iv;
  }
}