int main1(){
  int acnw, o, zrd, z;

  acnw=(1%27)+4;
  o=(1%40)+2;
  zrd=0;
  z=16;

  while (o!=zrd) {
      zrd = o;
      o = (o+acnw/o)/2;
      z = z+(o%2);
  }

}
