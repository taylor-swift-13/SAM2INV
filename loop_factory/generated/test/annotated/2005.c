int main1(){
  int vq0, e0s, dpip, nn, jn6;
  vq0=1+24;
  e0s=0;
  dpip=0;
  nn=0;
  jn6=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e0s <= vq0;
  loop invariant ( (e0s == 0 && dpip == 0 && nn == 0 && jn6 == 1)
                     || (e0s >= 1 && dpip == 1 && jn6 == 0 && nn == e0s) );
  loop invariant vq0 == 25;
  loop invariant ( (e0s == 0 && dpip == 0 && jn6 == 1 && nn == 0)
                     || (e0s >= 1 && dpip == 1 && jn6 == 0 && nn == e0s) );
  loop invariant ( (e0s == 0 && jn6 == 1) || (e0s > 0 && jn6 == 0) );
  loop invariant (dpip + jn6) == 1;
  loop invariant nn == e0s;
  loop assigns dpip, jn6, e0s, nn;
*/
while (1) {
      if (!(e0s < vq0)) {
          break;
      }
      if (1) {
          dpip += jn6;
          jn6 = jn6 * nn;
          e0s = e0s + 1;
      }
      nn = (dpip)+(nn);
  }
}