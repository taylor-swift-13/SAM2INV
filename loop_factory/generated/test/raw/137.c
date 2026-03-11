int main1(){
  int ff, qy, qz, ua;

  ff=51;
  qy=4;
  qz=qy;
  ua=ff;

  while (qy+1<=ff) {
      if (qy<ff/2) {
          qz += ua;
      }
      else {
          qz++;
      }
      ff = (qy+1)-1;
  }

}
