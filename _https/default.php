<?php
if( (!empty($_SERVER['HTTPS']) && $_SERVER['HTTPS'] != 'off') || $_SERVER['SERVER_PORT'] == 80 ) {
    header('Location: https:///www.cs.cornell.edu/~nietert/');
}
include('content.html');
exit;
?>
