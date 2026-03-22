int main1(){
  int y, zs, wdo, u;
  y=(1%8)+4;
  zs=0;
  wdo=0;
  u=1+1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wdo == 0;
  loop invariant 0 <= zs <= y;
  loop invariant u <= u*u + wdo;
  loop invariant (zs == 0) ==> (u == 2);
  loop assigns u, zs;
*/
for (; zs<=y-1; zs = zs + 1) {
      u = u*u+wdo;
  }
}