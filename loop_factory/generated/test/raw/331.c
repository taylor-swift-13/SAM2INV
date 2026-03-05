int main1(){
  int j6ro, hh, e, gb;

  j6ro=(1%23)+13;
  hh=0;
  e=0;
  gb=1;

  for (; e>0&&gb<=j6ro; hh++) {
      if (e>gb) {
          e = e - gb;
      }
      else {
          e = 0;
      }
      e += 1;
      gb = gb + 1;
  }

}
