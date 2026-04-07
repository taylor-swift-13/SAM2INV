int main1(){
  int hge, de, xp, psy;

  hge=1*2;
  de=0;
  xp=hge;
  psy=0;

  while (1) {
      if (!(de < hge)) {
          break;
      }
      psy = psy + 3;
      de = de + 1 + ((hge - de) / (de + 2));
      xp++;
  }

}
