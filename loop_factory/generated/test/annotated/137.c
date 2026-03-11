int main1(){
  int ff, qy, qz, ua;
  ff=51;
  qy=4;
  qz=qy;
  ua=ff;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qz >= qy;
  loop invariant ua == 51;
  loop invariant qy == 4;
  loop invariant (ff == 51) || (ff == qy);
  loop invariant ((ff == 51) <==> (qz == 4));
  loop invariant (qz <= 4 + ua);
  loop assigns qz, ff;
*/
while (qy+1<=ff) {
      if (qy<ff/2) {
          qz += ua;
      }
      else {
          qz++;
      }
      ff = (qy+1)-1;
  }
}