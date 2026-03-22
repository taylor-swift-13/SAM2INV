int main1(){
  int ye, ny, wow, tfv, qz, v9;

  ye=0;
  ny=0;
  wow=0;
  tfv=(1%50)+20;
  qz=(1%8)+2;
  v9=ye;

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
