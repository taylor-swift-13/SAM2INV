int main1(){
  int pia, y9, cp2;

  pia=(1%20)+5;
  y9=(1%20)+5;
  cp2=(1%20)+5;

  while (pia>0) {
      if (y9>0) {
          if (cp2>0) {
              pia = pia - 1;
              y9 -= 1;
              cp2--;
          }
      }
  }

}
