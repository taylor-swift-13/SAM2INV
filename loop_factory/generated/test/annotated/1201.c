int main1(){
  int ye, ny, wow, tfv, qz, v9;
  ye=0;
  ny=0;
  wow=0;
  tfv=(1%50)+20;
  qz=(1%8)+2;
  v9=ye;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= tfv <= 21;
  loop invariant 3 <= qz;
  loop invariant ye == 0;
  loop invariant tfv + qz == 24;
  loop invariant wow == qz - 3;
  loop invariant ny == 0;
  loop invariant v9  == (21 - tfv) * (22 - tfv) / 2;
  loop assigns ny, wow, tfv, v9, qz;
*/
while (1) {
      if (!(tfv!=0)) {
          break;
      }
      if (wow+1==qz) {
          ny = ny + 1;
          wow = 0;
      }
      else {
          wow++;
      }
      tfv--;
      v9 = v9 + wow;
      qz++;
      qz += ye;
  }
}