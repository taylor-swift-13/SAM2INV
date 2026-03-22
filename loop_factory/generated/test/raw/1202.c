int main1(){
  int kog, zzhg, uv5, truw;

  kog=0;
  zzhg=0;
  uv5=(1%50)+20;
  truw=(1%8)+2;

  while (uv5!=0) {
      if (zzhg+1==truw) {
          kog = kog + 1;
          zzhg = 0;
      }
      else {
          zzhg++;
      }
      uv5--;
      truw = truw + kog;
  }

}
