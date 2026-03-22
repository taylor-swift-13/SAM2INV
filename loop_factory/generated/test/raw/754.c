int main1(){
  int t9, cz, xey, qfc, hbu;

  t9=(1%20)+1;
  cz=(1%25)+1;
  xey=0;
  qfc=0;
  hbu=12;

  while (cz!=0) {
      if (cz%2==1) {
          xey = xey + t9;
          cz = cz - 1;
      }
      else {
      }
      t9 = 2*t9;
      cz = cz/2;
      hbu = ((cz%6))+(hbu);
      qfc = qfc*4;
  }

}
