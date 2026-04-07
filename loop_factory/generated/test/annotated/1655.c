int main1(){
  int br, tb9v, qz, aun;
  br=(1%39)+18;
  tb9v=0;
  qz=br;
  aun=tb9v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aun == 0;
  loop invariant qz == br;
  loop invariant 0 <= tb9v;
  loop invariant tb9v <= br;
  loop assigns qz, tb9v, aun;
*/
while (tb9v < br) {
      qz += aun;
      tb9v += 1;
      aun += aun;
  }
}