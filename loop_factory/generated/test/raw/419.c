int main1(){
  int wu, y, oy, y1m, il, meo;

  wu=1;
  y=wu;
  oy=9;
  y1m=0;
  il=1;
  meo=0;

  while (oy>0&&y<wu) {
      if (oy<=il) {
          meo = oy;
      }
      else {
          meo = il;
      }
      il = il + 1;
      oy = oy - meo;
      y++;
      y1m = y1m + meo;
  }

}
