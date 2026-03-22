int main1(){
  int xfx2, il, ba, x1c, ya6y;

  xfx2=76;
  il=0;
  ba=(1%40)+2;
  x1c=0;
  ya6y=5;

  while (ba!=x1c) {
      x1c = ba;
      ba = (ba+xfx2/ba)/2;
      ya6y = ya6y+ba-ba;
  }

  while (1) {
      if (!(ba!=il)) {
          break;
      }
      il = ba;
      ba = (ba+xfx2/ba)/2;
      x1c = x1c+(ba%7);
  }

}
