int main1(){
  int z81, iz, btf, wqz;
  z81=(1%17)+17;
  iz=0;
  btf=0;
  wqz=iz;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wqz == 0;
  loop invariant btf == 2*iz;
  loop invariant 0 <= iz <= z81;
  loop assigns wqz, btf, iz;
*/
while (1) {
      wqz = wqz + 1;
      btf++;
      wqz--;
      btf = (1)+(btf);
      iz += 1;
      if (iz>=z81) {
          break;
      }
  }
}