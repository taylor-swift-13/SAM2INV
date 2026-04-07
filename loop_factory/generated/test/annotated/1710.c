int main1(){
  int d, yny, sd3u;
  d=(1%29)+8;
  yny=0;
  sd3u=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sd3u == 3 + 4*yny;
  loop invariant 0 <= yny <= d;
  loop invariant d == 9;
  loop assigns yny, sd3u;
*/
while (yny < d) {
      yny++;
      sd3u = sd3u + 3;
      sd3u += 1;
  }
}