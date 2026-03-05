int main1(int j){
  int x2, ai, u76;

  x2=(j%19)+6;
  ai=0;
  u76=3;

  while (ai<x2) {
      u76 = ai%5;
      if (ai>=u76) {
          u76 = (ai-u76)%5;
          u76 = u76+u76-u76;
      }
      else {
          u76 += u76;
      }
      j += u76;
      ai++;
  }

}
