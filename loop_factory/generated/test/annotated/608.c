int main1(){
  int id, w, u1jv, ej;
  id=194;
  w=id;
  u1jv=w;
  ej=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u1jv - ej*w == -1358;
  loop invariant w >= 194;
  loop invariant u1jv == 8*w - 1358;
  loop invariant w >= id/2;
  loop assigns u1jv, w;
*/
while (w-1>=0) {
      if (!(!(w<id/2))) {
          u1jv = u1jv + 1;
      }
      else {
          u1jv = u1jv + ej;
      }
      w += 1;
  }
}