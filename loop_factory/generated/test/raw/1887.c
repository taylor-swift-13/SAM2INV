int main1(){
  int spo, en, hw, yjl, m, w, s1, h, nd6;

  spo=41;
  en=0;
  hw=spo;
  yjl=6;
  m=-8;
  w=en;
  s1=spo;
  h=en;
  nd6=-8;

  while (en < spo) {
      if (!(!((en % 3) == 0))) {
      }
      else {
          hw++;
          yjl += 2;
      }
      if ((en % 3) == 1) {
          m = m * 2;
          w += 1;
      }
      else {
      }
      if ((en % 3) == 2) {
          h += 1;
          nd6 = nd6 + 3;
      }
      else {
      }
      s1 = s1 + w;
      en++;
      s1 += s1;
  }

}
