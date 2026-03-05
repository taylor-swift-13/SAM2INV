int main1(){
  int b, g, iq;

  b=(1%6)+4;
  g=0;
  iq=g;

  while (1) {
      if (iq+3<=b) {
          iq = iq + 3;
      }
      else {
          iq = b;
      }
      iq += iq;
      iq = iq + 5;
      g++;
      if (g>=b) {
          break;
      }
  }

}
