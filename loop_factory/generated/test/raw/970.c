int main1(){
  int ov, de, ui;

  ov=(1%20)+5;
  de=(1%20)+5;
  ui=(1%20)+5;

  while (ov>0) {
      if (de>0) {
          if (ui>0) {
              ov -= 1;
              de--;
              ui--;
          }
      }
      ui += ui;
  }

}
