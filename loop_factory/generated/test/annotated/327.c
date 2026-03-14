int main1(int j){
  int t6z, v2e, x, a, yiw, tf7c;
  t6z=65;
  v2e=0;
  x=0;
  a=0;
  yiw=t6z;
  tf7c=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a >= 0;
  loop invariant a <= t6z;
  loop invariant x == j * a;
  loop invariant tf7c == 4 + 2 * a;
  loop invariant yiw == t6z + a*(a+1)/2;
  loop invariant yiw == 65 + a*(a+1)/2;
  loop assigns a, x, tf7c, yiw;
*/
while (1) {
      if (!(a<t6z)) {
          break;
      }
      a++;
      x += j;
      tf7c += 2;
      yiw = yiw + a;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == t6z * j;
  loop invariant a >= t6z;
  loop invariant v2e - j * a == - j * t6z;
  loop invariant tf7c >= 4;
  loop invariant yiw >= 65;
  loop assigns a, v2e, tf7c;
*/
while (a<x) {
      v2e += j;
      a++;
      tf7c = tf7c + v2e;
      tf7c = tf7c + yiw;
  }
}