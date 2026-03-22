int main1(){
  int gh, fb82, ee, v0r;

  gh=1*2;
  fb82=(1%40)+2;
  ee=0;
  v0r=gh;

  while (1) {
      if (!(fb82!=ee)) {
          break;
      }
      ee = fb82;
      fb82 = (fb82+gh/fb82)/2;
      v0r = v0r+(fb82%4);
  }

}
